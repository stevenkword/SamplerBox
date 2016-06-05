#
#  SamplerBox 
#
#  author:    Joseph Ernest (twitter: @JosephErnest, mail: contact@samplerbox.org)
#  url:       http://www.samplerbox.org/
#  license:   Creative Commons ShareAlike 3.0 (http://creativecommons.org/licenses/by-sa/3.0/)
#
#  samplerbox.py: Main file
#



#########################################
##  LOCAL  
##  CONFIG
#########################################

AUDIO_DEVICE_ID = 0                     # change this number to use another soundcard
SAMPLES_DIR = "/sdsamples/"                       # The root directory containing the sample-sets. Example: "/media/" to look for samples on a USB stick / SD card
#SAMPLES_DIR = "/media/"                       # The root directory containing the sample-sets. Example: "/media/" to look for samples on a USB stick / SD card
USE_SERIALPORT_MIDI = True             # Set to True to enable MIDI IN via SerialPort (e.g. RaspberryPi's GPIO UART pins)
USE_I2C_7SEGMENTDISPLAY = True         # Set to True to use a 7-segment display via I2C 
USE_BUTTONS = True                     # Set to True to use momentary buttons (connected to RaspberryPi's GPIO pins) to change preset
MAX_POLYPHONY = 80                      # This can be set higher, but 80 is a safe value


#########################################
##  IMPORT 
##  MODULES
#########################################

import wave
import time
import numpy
import os, re
import pyaudio
import threading   
from chunk import Chunk
import struct
import rtmidi_python as rtmidi
import samplerbox_audio

###### Trentin's Modified 9.8.15
#import
import RPi.GPIO as GPIO
import time
import subprocess

import socket
import fcntl
import struct

# Define GPIO to LCD mapping

LCD_RS = 7
LCD_E  = 8
LCD_D4 = 25
LCD_D5 = 24
LCD_D6 = 23
LCD_D7 = 27


# Define some device constants
LCD_WIDTH = 16    # Maximum characters per line
LCD_CHR = True
LCD_CMD = False

LCD_LINE_1 = 0x80 # LCD RAM address for the 1st line
LCD_LINE_2 = 0xC0 # LCD RAM address for the 2nd line
# Main program block

GPIO.setmode(GPIO.BCM)       # Use BCM GPIO numbers
GPIO.setup(LCD_E, GPIO.OUT)  # E
GPIO.setup(LCD_RS, GPIO.OUT) # RS
GPIO.setup(LCD_D4, GPIO.OUT) # DB4
GPIO.setup(LCD_D5, GPIO.OUT) # DB5
GPIO.setup(LCD_D6, GPIO.OUT) # DB6
GPIO.setup(LCD_D7, GPIO.OUT) # DB7



# Timing constants
E_PULSE = 0.0005
E_DELAY = 0.0005

def lcd_init():
  # Initialise display
  lcd_byte(0x33,LCD_CMD) # 110011 Initialise
  lcd_byte(0x32,LCD_CMD) # 110010 Initialise
  lcd_byte(0x06,LCD_CMD) # 000110 Cursor move direction
  lcd_byte(0x0C,LCD_CMD) # 001100 Display On,Cursor Off, Blink Off
  lcd_byte(0x28,LCD_CMD) # 101000 Data length, number of lines, font size
  lcd_byte(0x01,LCD_CMD) # 000001 Clear display
  time.sleep(E_DELAY)


def lcd_byte(bits, mode):
  # Send byte to data pins
  # bits = data
  # mode = True  for character
  #        False for command

  GPIO.output(LCD_RS, mode) # RS

  # High bits
  GPIO.output(LCD_D4, False)
  GPIO.output(LCD_D5, False)
  GPIO.output(LCD_D6, False)
  GPIO.output(LCD_D7, False)
  if bits&0x10==0x10:
    GPIO.output(LCD_D4, True)
  if bits&0x20==0x20:
    GPIO.output(LCD_D5, True)
  if bits&0x40==0x40:
    GPIO.output(LCD_D6, True)
  if bits&0x80==0x80:
    GPIO.output(LCD_D7, True)

  # Toggle 'Enable' pin
  lcd_toggle_enable()
  # Low bits
  GPIO.output(LCD_D4, False)
  GPIO.output(LCD_D5, False)
  GPIO.output(LCD_D6, False)
  GPIO.output(LCD_D7, False)
  if bits&0x01==0x01:
    GPIO.output(LCD_D4, True)
  if bits&0x02==0x02:
    GPIO.output(LCD_D5, True)
  if bits&0x04==0x04:
    GPIO.output(LCD_D6, True)
  if bits&0x08==0x08:
    GPIO.output(LCD_D7, True)

  # Toggle 'Enable' pin
  lcd_toggle_enable()

def lcd_toggle_enable():
  # Toggle enable
  time.sleep(E_DELAY)
  GPIO.output(LCD_E, True)
  time.sleep(E_PULSE)
  GPIO.output(LCD_E, False)
  time.sleep(E_DELAY)


def lcd_string(message,line):
  # Send string to display




  message = message.ljust(LCD_WIDTH," ")

  lcd_byte(line, LCD_CMD)

  for i in range(LCD_WIDTH):
    lcd_byte(ord(message[i]),LCD_CHR)


# Initialise display
lcd_init()
time.sleep(0.1)
lcd_string("Sampler Box ",LCD_LINE_1)
lcd_string("Trentin's Lab ",LCD_LINE_2)

def get_ip_address(ifname):
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    return socket.inet_ntoa(fcntl.ioctl(
        s.fileno(),
        0x8915,  # SIOCGIFADDR
        struct.pack('256s', ifname[:15])
    )[20:24])

###### END Trentin's Modified 9.8.15


#########################################
##  SLIGHT MODIFICATION OF PYTHON'S WAVE MODULE
##  TO READ CUE MARKERS & LOOP MARKERS
#########################################

class waveread(wave.Wave_read):
    def initfp(self, file):
        self._convert = None
        self._soundpos = 0
        self._cue = []
        self._loops = []
        self._ieee = False
        self._file = Chunk(file, bigendian = 0)
        if self._file.getname() != 'RIFF':
            raise Error, 'file does not start with RIFF id'
        if self._file.read(4) != 'WAVE':
            raise Error, 'not a WAVE file'
        self._fmt_chunk_read = 0
        self._data_chunk = None
        while 1:
            self._data_seek_needed = 1
            try:
                chunk = Chunk(self._file, bigendian = 0)
            except EOFError:
                break
            chunkname = chunk.getname()
            if chunkname == 'fmt ':
                self._read_fmt_chunk(chunk)
                self._fmt_chunk_read = 1
            elif chunkname == 'data':
                if not self._fmt_chunk_read:
                    raise Error, 'data chunk before fmt chunk'
                self._data_chunk = chunk
                self._nframes = chunk.chunksize // self._framesize
                self._data_seek_needed = 0
            elif chunkname == 'cue ':
                numcue = struct.unpack('<i',chunk.read(4))[0]
                for i in range(numcue): 
                  id, position, datachunkid, chunkstart, blockstart, sampleoffset = struct.unpack('<iiiiii',chunk.read(24))
                  self._cue.append(sampleoffset)
            elif chunkname == 'smpl':
                manuf, prod, sampleperiod, midiunitynote, midipitchfraction, smptefmt, smpteoffs, numsampleloops, samplerdata = struct.unpack('<iiiiiiiii',chunk.read(36))
                for i in range(numsampleloops):
                   cuepointid, type, start, end, fraction, playcount = struct.unpack('<iiiiii',chunk.read(24)) 
                   self._loops.append([start,end]) 
            chunk.skip()
        if not self._fmt_chunk_read or not self._data_chunk:
            raise Error, 'fmt chunk and/or data chunk missing'

    def getmarkers(self):
        return self._cue
        
    def getloops(self):
        return self._loops



#########################################
##  MIXER CLASSES
#########################################

class PlayingSound:
    def __init__(self, sound, note):
        self.sound = sound
        self.pos = 0
        self.fadeoutpos = 0
        self.isfadeout = False
        self.note = note

    def fadeout(self, i):
        self.isfadeout = True
        
    def stop(self):
        try: playingsounds.remove(self) 
        except: pass

class Sound:
    def __init__(self, filename, midinote, velocity):
        wf = waveread(filename)
        self.fname = filename
        self.midinote = midinote
        self.velocity = velocity
        if wf.getloops(): 
            self.loop = wf.getloops()[0][0]
            self.nframes = wf.getloops()[0][1] + 2
        else:
            self.loop = -1
            self.nframes = wf.getnframes()

        self.data = self.frames2array(wf.readframes(self.nframes), wf.getsampwidth(), wf.getnchannels())

        wf.close()            

    def play(self, note):
        snd = PlayingSound(self, note)
        playingsounds.append(snd)
        return snd

    def frames2array(self, data, sampwidth, numchan):
        if sampwidth == 2:
            npdata = numpy.fromstring(data, dtype = numpy.int16)
        elif sampwidth == 3:
            npdata = samplerbox_audio.binary24_to_int16(data, len(data)/3)
        if numchan == 1: 
            npdata = numpy.repeat(npdata, 2)
        return npdata

FADEOUTLENGTH = 30000
FADEOUT = numpy.linspace(1., 0., FADEOUTLENGTH)            # by default, float64
FADEOUT = numpy.power(FADEOUT, 6)
FADEOUT = numpy.append(FADEOUT, numpy.zeros(FADEOUTLENGTH, numpy.float32)).astype(numpy.float32)
SPEED = numpy.power(2, numpy.arange(0.0, 84.0)/12).astype(numpy.float32)

samples = {}
playingnotes = {}
sustainplayingnotes = []
sustain = False
playingsounds = []
globalvolume = 10 ** (-12.0/20)    #  -12dB default global volume

#########################################
##  AUDIO AND MIDI CALLBACKS
#########################################

def AudioCallback(in_data, frame_count, time_info, status):
    global playingsounds
    rmlist = []
    playingsounds = playingsounds[-MAX_POLYPHONY:]    
    b = samplerbox_audio.mixaudiobuffers(playingsounds, rmlist, frame_count, FADEOUT, FADEOUTLENGTH, SPEED)
    for e in rmlist:
        try: playingsounds.remove(e)
        except: pass
    b *= globalvolume
    odata = (b.astype(numpy.int16)).tostring()   
    return (odata, pyaudio.paContinue)


def MidiCallback(message, time_stamp):
    global playingnotes, sustain, sustainplayingnotes
    global preset
    messagetype = message[0] >> 4
    messagechannel = (message[0] & 15) + 1
    note = message[1] if len(message) > 1 else None
    midinote = note
    velocity = message[2] if len(message) > 2 else None

    if messagetype == 9 and velocity == 0: messagetype = 8

    if messagetype == 9:    # Note on
        try:
          playingnotes.setdefault(midinote,[]).append(samples[midinote, velocity].play(note))
        except:
          pass

    elif messagetype == 8:  # Note off
        if midinote in playingnotes:
            for n in playingnotes[midinote]: 
                if sustain:
                    sustainplayingnotes.append(n)
                else:
                    n.fadeout(50)
            playingnotes[midinote] = []

    elif messagetype == 12: # Program change
        print 'Program change ' + str(note)
        preset = note
        print note
        LoadSamples()

    elif (messagetype == 11) and (note == 64) and (velocity < 64): # sustain pedal off
        for n in sustainplayingnotes:
            n.fadeout(50)
        sustainplayingnotes = []       
        sustain = False

    elif (messagetype == 11) and (note == 64) and (velocity >= 64): # sustain pedal on
        sustain = True



#########################################
##  LOAD SAMPLES
#########################################

LoadingThread = None            
LoadingInterrupt = False

def LoadSamples():
    global LoadingThread
    global LoadingInterrupt

    if LoadingThread:
        LoadingInterrupt = True
        LoadingThread.join()
        LoadingThread = None
    
    LoadingInterrupt = False
    LoadingThread = threading.Thread(target = ActuallyLoad)
    LoadingThread.daemon = True
    LoadingThread.start()

NOTES = ["c", "c#", "d", "d#", "e", "f", "f#", "g", "g#", "a", "a#", "b"]

###################################################
def ActuallyLoad():    
    global preset
    global samples
    global playingsounds
    global globalvolume
    playingsounds = []
    samples = {}    
    dirname = next((f for f in os.listdir(SAMPLES_DIR) if f.startswith("%d " % preset)), None)      # or next(glob.iglob("blah*"), None)
    globalvolume = 10 ** (-12.0/20)    #  -12dB default global volume
    if dirname:
        dirname = os.path.join(SAMPLES_DIR, dirname)
    if not dirname: 
        ###### Trentin's Modified 9.8.15
        lcd_string("Preset empty "+str(preset),LCD_LINE_1)
        lcd_string("Trentin's Lab ",LCD_LINE_2)
        ###### END Trentin's Modified 9.8.15
        print 'Preset empty: %s' % preset
        display("E%03d" % preset)
        return
    ###### Trentin's Modified 9.8.15
    lcd_string("Loading ... "+str(preset),LCD_LINE_1)
    ###### END Trentin's Modified 9.8.15
    name_preset=dirname[11:26]+" "
    lcd_string(name_preset,LCD_LINE_2)
    print 'Preset loading: %s' % preset
    display("L%03d" % preset)
    definitionfname = os.path.join(dirname, "%d.txt" % preset)                     # parse the sample-set definition file
    if not os.path.isfile(definitionfname): 
        definitionfname = os.path.join(dirname, "definition.txt")
    if os.path.isfile(definitionfname):
        with open(definitionfname, 'r') as definitionfile:
            for i, pattern in enumerate(definitionfile):
                try:
                    if r'%%volume' in pattern:        # %%paramaters are global parameters
                        globalvolume *= 10 ** (float(pattern.split('=')[1].strip()) / 20)
                        continue
                    defaultparams = { 'midinote': '0', 'velocity': '127', 'notename': '' }
                    if len(pattern.split(',')) > 1:
                        defaultparams.update(dict([item.split('=') for item in pattern.split(',', 1)[1].replace(' ','').replace('%', '').split(',')]))
                    pattern = pattern.split(',')[0]
                    pattern = pattern.replace("%midinote", r"(?P<midinote>\d+)").replace("%velocity", r"(?P<velocity>\d+)").replace("%notename", r"(?P<notename>[A-Ga-g]#?[0-9])").replace("*", r".*").strip()
                    for fname in os.listdir(dirname):
                        if LoadingInterrupt: 
                            return
                        m = re.match(pattern, fname)
                        if m:
                            info = m.groupdict()
                            midinote = int(info.get('midinote', defaultparams['midinote']))
                            velocity = int(info.get('velocity', defaultparams['velocity']))
                            notename = info.get('notename', defaultparams['notename'])
                            if notename: midinote = NOTES.index(notename[:-1].lower()) + (int(notename[-1])+2) * 12
                            samples[midinote, velocity] = Sound(os.path.join(dirname, fname), midinote, velocity)
                except:
                    print "Error in definition file, skipping line %s." % (i+1)

    else:
        for midinote in range(0, 127): 
            if LoadingInterrupt: 
                return
            file = os.path.join(dirname, "%d.wav" % midinote)
            if os.path.isfile(file):
                samples[midinote, 127] = Sound(file, midinote, 127)             

    initial_keys = set(samples.keys())
    for midinote in xrange(128):
        lastvelocity = None
        for velocity in xrange(128):
            if (midinote, velocity) not in initial_keys:
                samples[midinote, velocity] = lastvelocity
            else: 
                if not lastvelocity: 
                    for v in xrange(velocity): samples[midinote, v] = samples[midinote, velocity]
                lastvelocity = samples[midinote, velocity]
        if not lastvelocity: 
            for velocity in xrange(128): 
                try: samples[midinote, velocity] = samples[midinote-1, velocity]
                except: pass
    if len(initial_keys) > 0:
    ###### Trentin's Modified 9.8.15
        lcd_string("Loaded: "+str(preset),LCD_LINE_1)
    ###### END Trentin's Modified 9.8.15
        print 'Preset loaded: ' + str(preset) 
        display("%04d" % preset)    
    else:
    ###### Trentin's Modified 9.8.15
        lcd_string("Preset empty "+str(preset),LCD_LINE_1)
        lcd_string("Trentin's Lab ",LCD_LINE_1)
    ###### END Trentin's Modified 9.8.15
        print 'Preset empty: ' + str(preset) 
        display("E%03d" % preset)    



#########################################
##  OPEN AUDIO DEVICE
#########################################

p = pyaudio.PyAudio()
stream = p.open(format = pyaudio.paInt16, channels = 2, rate = 44100, frames_per_buffer = 512, output = True, input = False, output_device_index = AUDIO_DEVICE_ID, stream_callback = AudioCallback)
print 'Opened audio: '+ p.get_device_info_by_index(AUDIO_DEVICE_ID)['name']



#########################################
##  BUTTONS THREAD (RASPBERRY PI GPIO) 
#########################################

if USE_BUTTONS:
    import RPi.GPIO as GPIO

    lastbuttontime = 0

    def Buttons():
        GPIO.setmode(GPIO.BCM)
        GPIO.setup(18, GPIO.IN, pull_up_down=GPIO.PUD_UP)
        GPIO.setup(17, GPIO.IN, pull_up_down=GPIO.PUD_UP)    
        ### GPIO Per VOLUME
        GPIO.setup(12, GPIO.IN, pull_up_down=GPIO.PUD_UP)    
        GPIO.setup(22, GPIO.IN, pull_up_down=GPIO.PUD_UP) # VOL -
        global preset, lastbuttontime
###### Trentin's Modified 9.8.15
        global timeNOW
        timeNOW=0
        ####
        while True:
          now = time.time()
###### Trentin's Modified 9.8.15
          if not GPIO.input(18) and not GPIO.input(17) and (now - lastbuttontime) > 0.2:
              timeNOW=time.time()
              ip = get_ip_address('eth0')
              lcd_string("IP: "+ip+" "+str(preset),LCD_LINE_1)
              #lcd_string(str(timeNOW),LCD_LINE_2)
              lastbuttontime = now
###### END Trentin's Modified 9.8.15
          if not GPIO.input(18) and (now - lastbuttontime) > 0.2:
            lastbuttontime = now 
            preset -= 1
            if preset < 0: preset = 0
            #if preset < 0: preset = 127
            LoadSamples()

          elif not GPIO.input(17)  and (now - lastbuttontime) > 0.2:
            lastbuttontime = now
            preset += 1  
            if preset > 127: preset = 0
            LoadSamples()      

###### Trentin's Modified 9.8.15
          elif not GPIO.input(12) and (now - lastbuttontime) > 0.2:
            timeNOW=time.time()
            lastbuttontime = now
            p = subprocess.Popen(["amixer","get","PCM,0"], stdout=subprocess.PIPE)
            out = p.stdout.read()
            pos1=out.find("[")
            pos2=out.find("]")
            vol=int(out[pos1+1:pos2-1])+5
            if vol > 100:
               vol=100
            p = subprocess.Popen(["amixer","set","PCM,0",str(vol)+"%"], stdout=subprocess.PIPE)
            lcd_string("Volume "+str(vol)+"%",LCD_LINE_1)
            lastbuttontime = now

          elif not GPIO.input(22)  and (now - lastbuttontime) > 0.2:
            timeNOW=time.time()
            lastbuttontime = now
            p = subprocess.Popen(["amixer","get","PCM,0"], stdout=subprocess.PIPE)
            out = p.stdout.read()
            pos1=out.find("[")
            pos2=out.find("]")
            vol=int(out[pos1+1:pos2-1])-5
            if vol < 0:
               vol=0
            p = subprocess.Popen(["amixer","set","PCM,0",str(vol)+"%"], stdout=subprocess.PIPE)
            lcd_string("Volume "+str(vol)+"%",LCD_LINE_1)
            lastbuttontime = now

###### END Trentin's Modified 9.8.15
          time.sleep(0.02)

    ButtonsThread = threading.Thread(target = Buttons)
    ButtonsThread.daemon = True
    ButtonsThread.start()    



#########################################
##  7-SEGMENT DISPLAY 
##  
#########################################

if USE_I2C_7SEGMENTDISPLAY:
    import smbus

    bus = smbus.SMBus(1)     # using I2C

    def display(s):
        for k in '\x76\x79\x00' + s:     # position cursor at 0
            try:
                bus.write_byte(0x71, ord(k))
            except:
                try: bus.write_byte(0x71, ord(k))
                except: pass
            time.sleep(0.002)

    display('----')
    time.sleep(0.5)

else:

    def display(s):
        pass    



#########################################
##  MIDI IN via SERIAL PORT
##  
#########################################

if USE_SERIALPORT_MIDI:
    import serial

    ser = serial.Serial('/dev/ttyAMA0', baudrate=38400)       # see hack in /boot/cmline.txt : 38400 is 31250 baud for MIDI!

    def MidiSerialCallback():
        message = [0, 0, 0]
        while True:
          i = 0
          while i < 3:
            data = ord(ser.read(1)) # read a byte
            if data >> 7 != 0:  
              i = 0      # status byte!   this is the beginning of a midi message: http://www.midi.org/techspecs/midimessages.php
            message[i] = data
            i += 1
            if i == 2 and message[0] >> 4 == 12:  # program change: don't wait for a third byte: it has only 2 bytes
              message[2] = 0
              i = 3
          MidiCallback(message, None)

    MidiThread = threading.Thread(target = MidiSerialCallback)
    MidiThread.daemon = True
    MidiThread.start()



#########################################
##  LOAD FIRST SOUNDBANK
##  
#########################################     

preset = 0
LoadSamples()



#########################################
##  MIDI DEVICES DETECTION
##  MAIN LOOP
#########################################

midi_in = [rtmidi.MidiIn()]
previous = []
while True:
    for port in midi_in[0].ports:
        if port not in previous and 'Midi Through' not in port:
            midi_in.append(rtmidi.MidiIn())
            midi_in[-1].callback = MidiCallback        
            midi_in[-1].open_port(port)       
            print 'Opened MIDI: '+ port
    previous = midi_in[0].ports
    time.sleep(2)
 
